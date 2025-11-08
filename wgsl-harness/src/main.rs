use anyhow::Result;
use wgpu::util::DeviceExt;

const WG_SIZE: u32 = 256;
const WGSL_SRC: &str = include_str!(env!("WGSL_KERNEL_PATH"));

fn main() -> Result<()> {
    let wgsl = WGSL_SRC;
    let n = WG_SIZE as usize;
    let input: Vec<i32> = (0..n as i32).collect();

    let output = pollster::block_on(run_compute(wgsl, &input))?;
    let expected = exclusive_scan(&input);
    println!("input[0..8]    = {:?}", &input[..8.min(input.len())]);
    println!("gpu[0..8]      = {:?}", &output[..8.min(output.len())]);
    println!("expected[0..8] = {:?}", &expected[..8.min(expected.len())]);
    if output != expected {
        anyhow::bail!("GPU result does not match exclusive scan output");
    }

    Ok(())
}

fn exclusive_scan(input: &[i32]) -> Vec<i32> {
    let mut acc = 0;
    input
        .iter()
        .map(|&x| {
            let out = acc;
            acc += x;
            out
        })
        .collect()
}

async fn run_compute(wgsl: &str, input: &[i32]) -> Result<Vec<i32>> {
    let instance = wgpu::Instance::default();
    let adapter = instance
        .request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            force_fallback_adapter: false,
            compatible_surface: None,
        })
        .await?;

    let info = adapter.get_info();
    eprintln!("Using adapter: {} ({:?})", info.name, info.backend);

    let (device, queue) = adapter
        .request_device(&wgpu::DeviceDescriptor {
            label: Some("device"),
            required_features: wgpu::Features::empty(),
            required_limits: wgpu::Limits::default(),
            experimental_features: wgpu::ExperimentalFeatures::default(),
            memory_hints: wgpu::MemoryHints::default(),
            trace: wgpu::Trace::default(),
        })
        .await?;

    let size_bytes = (input.len() * std::mem::size_of::<i32>()) as wgpu::BufferAddress;

    let storage = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some("storage"),
        contents: bytemuck::cast_slice(input),
        usage: wgpu::BufferUsages::STORAGE
            | wgpu::BufferUsages::COPY_SRC
            | wgpu::BufferUsages::COPY_DST,
    });

    let readback = device.create_buffer(&wgpu::BufferDescriptor {
        label: Some("readback"),
        size: size_bytes,
        usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });

    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("kernel"),
        source: wgpu::ShaderSource::Wgsl(wgsl.into()),
    });

    let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("bgl0"),
        entries: &[wgpu::BindGroupLayoutEntry {
            binding: 0,
            visibility: wgpu::ShaderStages::COMPUTE,
            ty: wgpu::BindingType::Buffer {
                ty: wgpu::BufferBindingType::Storage { read_only: false },
                has_dynamic_offset: false,
                min_binding_size: None,
            },
            count: None,
        }],
    });

    let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: Some("bg0"),
        layout: &bgl,
        entries: &[wgpu::BindGroupEntry {
            binding: 0,
            resource: storage.as_entire_binding(),
        }],
    });

    let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
        label: Some("pl"),
        bind_group_layouts: &[&bgl],
        push_constant_ranges: &[],
    });

    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: Some("compute"),
        layout: Some(&pipeline_layout),
        module: &shader,
        entry_point: Some("main"),
        compilation_options: wgpu::PipelineCompilationOptions::default(),
        cache: None,
    });

    let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
        label: Some("encoder"),
    });

    {
        let mut cpass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some("cpass"),
            ..Default::default()
        });
        cpass.set_pipeline(&pipeline);
        cpass.set_bind_group(0, &bind_group, &[]);
        cpass.dispatch_workgroups(1, 1, 1);
    }

    encoder.copy_buffer_to_buffer(&storage, 0, &readback, 0, size_bytes);
    queue.submit(Some(encoder.finish()));

    let slice = readback.slice(..);
    slice.map_async(wgpu::MapMode::Read, |_| {});
    device.poll(wgpu::PollType::wait_indefinitely())?;

    let data = slice.get_mapped_range();
    let out: Vec<i32> = bytemuck::cast_slice(&data).to_vec();
    drop(data);
    readback.unmap();

    Ok(out)
}
