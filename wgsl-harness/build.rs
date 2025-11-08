use std::{
    env,
    fs,
    path::PathBuf,
    process::{Command, Stdio},
};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    for path in [
        "../WGSL",
        "../Kernel",
        "../Effects",
        "../LanguageQuantale",
        "../lakefile.lean",
        "../lake-manifest.json",
        "../lean-toolchain",
    ] {
        println!("cargo:rerun-if-changed={path}");
    }

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let artifact_dir = manifest_dir.join(".generated");
    fs::create_dir_all(&artifact_dir).expect("failed to create artifact dir");
    let artifact_path = artifact_dir.join("kernel.wgsl");

    let status = Command::new("lake")
        .arg("exe")
        .arg("emitWGSL")
        .arg(&artifact_path)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .current_dir(manifest_dir.parent().expect("crate has parent"))
        .status()
        .expect("failed to run `lake exe emitWGSL`");

    if !status.success() {
        panic!("`lake exe emitWGSL` exited with {}", status);
    }

    let artifact_path = artifact_path
        .canonicalize()
        .unwrap_or(artifact_path);

    println!(
        "cargo:rustc-env=WGSL_KERNEL_PATH={}",
        artifact_path.display()
    );
}
