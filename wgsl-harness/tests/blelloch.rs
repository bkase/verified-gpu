use wgpu::util::DeviceExt;

const WGSL_SRC: &str = include_str!(env!("WGSL_KERNEL_PATH"));

#[test]
fn computes_exclusive_scan() {
    let wgsl = WGSL_SRC;
    let n = 256usize;
    let input: Vec<i32> = (0..n as i32).collect();

    let output = pollster::block_on(async {
        let instance = wgpu::Instance::default();
        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                force_fallback_adapter: false,
                compatible_surface: None,
            })
            .await
            .expect("no adapter");

        let (device, queue) = adapter
            .request_device(&wgpu::DeviceDescriptor {
                label: None,
                required_features: wgpu::Features::empty(),
                required_limits: wgpu::Limits::default(),
                experimental_features: wgpu::ExperimentalFeatures::default(),
                memory_hints: wgpu::MemoryHints::default(),
                trace: wgpu::Trace::default(),
            })
            .await
            .expect("device");

        let size_bytes = (input.len() * std::mem::size_of::<i32>()) as wgpu::BufferAddress;
        let storage = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("storage"),
            contents: bytemuck::cast_slice(&input),
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
        let bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bg0"),
            layout: &bgl,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: storage.as_entire_binding(),
            }],
        });
        let pl = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("pl"),
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let pipe = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("pipeline"),
            layout: Some(&pl),
            module: &shader,
            entry_point: Some("main"),
            compilation_options: Default::default(),
            cache: None,
        });

        let mut enc = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("encoder"),
        });
        {
            let mut c = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("cpass"),
                ..Default::default()
            });
            c.set_pipeline(&pipe);
            c.set_bind_group(0, &bg, &[]);
            c.dispatch_workgroups(1, 1, 1);
        }
        enc.copy_buffer_to_buffer(&storage, 0, &readback, 0, size_bytes);
        queue.submit(Some(enc.finish()));

        let slice = readback.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        device
            .poll(wgpu::PollType::wait_indefinitely())
            .expect("poll");
        let bytes = slice.get_mapped_range();
        let out: Vec<i32> = bytemuck::cast_slice(&bytes).to_vec();
        drop(bytes);
        readback.unmap();
        out
    });

    let expected: Vec<i32> = exclusive_scan(&input);
    assert_eq!(output, expected);
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
