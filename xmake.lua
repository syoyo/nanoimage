add_rules("mode.debug", "mode.release")

set_languages("c11", "c++17")

option("simd")
    set_default(false)
    set_showmenu(true)
    set_description("Enable optional x86 SIMD PNG helpers")

option("custom_png_codec")
    set_default(false)
    set_showmenu(true)
    set_description("Enable optional fpnge/fpng custom PNG codec bridge")

local core_sources = {
    "src/nanoimage_alloc.c",
    "src/nanoimage_write.c",
    "src/nanoimage_simd.c",
    "src/nanoimage_zlib.c",
    "src/nanoimage_png.c",
    "src/nanoimage_png_write.c",
    "src/nanoimage_jpeg.c",
    "src/nanoimage_jpeg_write.c",
    "src/nanoimage_bmp.c",
    "src/nanoimage_bmp_write.c",
    "src/nanoimage_tga.c",
    "src/nanoimage_tga_write.c",
    "src/nanoimage_gif.c",
    "src/nanoimage_gif_write.c"
}

local function add_core_sources()
    add_files(core_sources)
    if has_config("simd") or has_config("custom_png_codec") then
        add_defines("NANOIMAGE_ENABLE_SIMD")
        add_files("src/nanoimage_simd_sse2.c", {cxflags = "-msse2"})
        add_files("src/nanoimage_simd_sse41.c", {cxflags = "-msse4.1"})
        add_files("src/nanoimage_simd_avx.c", {cxflags = "-mavx"})
        add_files("src/nanoimage_simd_avx2.c", {cxflags = "-mavx2"})
    end
    if has_config("custom_png_codec") then
        add_defines("NANOIMAGE_ENABLE_CUSTOM_PNG_CODEC")
        add_files("src/nanoimage_fpnge_bridge.cc",
                  {cxxflags = {"-msse4.1", "-mpclmul", "-fno-strict-aliasing"}})
        add_files("src/nanoimage_fpng_bridge.cc",
                  {cxxflags = {"-msse4.1", "-mpclmul", "-fno-strict-aliasing"}})
    end
end

target("nanoimage_example")
    set_kind("binary")
    add_includedirs("include")
    add_files("examples/load_image.c")
    add_core_sources()
    add_links("m", "z")

target("nanoimage_test")
    set_kind("binary")
    add_includedirs("include")
    add_files("tests/test_nanoimage.c")
    add_core_sources()
    add_links("m", "z")

target("nanoimage_png_benchmark")
    set_kind("binary")
    add_includedirs("include")
    add_files("benchmarks/png_benchmark.c")
    add_core_sources()
    add_links("m", "z")

target("nanoimage_fuzz")
    set_kind("binary")
    set_toolchains("clang")
    add_includedirs("include")
    add_files("tests/fuzz/fuzz_nanoimage.c")
    add_core_sources()
    add_links("m", "z")
    add_cxflags("-fsanitize=fuzzer,address", {force = true})
    add_ldflags("-fsanitize=fuzzer,address", {force = true})

target("nanoimage_writer_fuzz")
    set_kind("binary")
    set_toolchains("clang")
    add_includedirs("include")
    add_files("tests/fuzz/fuzz_nanoimage_writer.c")
    add_core_sources()
    add_links("m", "z")
    add_cxflags("-fsanitize=fuzzer,address", {force = true})
    add_ldflags("-fsanitize=fuzzer,address", {force = true})
