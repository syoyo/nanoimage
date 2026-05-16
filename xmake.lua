add_rules("mode.debug", "mode.release")

set_languages("c11")

local core_sources = {
    "src/nanoimage_alloc.c",
    "src/nanoimage_write.c",
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

target("nanoimage_example")
    set_kind("binary")
    add_includedirs("include")
    add_files("examples/load_image.c")
    add_files(core_sources)
    add_links("m", "z")

target("nanoimage_test")
    set_kind("binary")
    add_includedirs("include")
    add_files("tests/test_nanoimage.c")
    add_files(core_sources)
    add_links("m", "z")

target("nanoimage_fuzz")
    set_kind("binary")
    set_toolchains("clang")
    add_includedirs("include")
    add_files("tests/fuzz/fuzz_nanoimage.c")
    add_files(core_sources)
    add_links("m", "z")
    add_cxflags("-fsanitize=fuzzer,address", {force = true})
    add_ldflags("-fsanitize=fuzzer,address", {force = true})

target("nanoimage_writer_fuzz")
    set_kind("binary")
    set_toolchains("clang")
    add_includedirs("include")
    add_files("tests/fuzz/fuzz_nanoimage_writer.c")
    add_files(core_sources)
    add_links("m", "z")
    add_cxflags("-fsanitize=fuzzer,address", {force = true})
    add_ldflags("-fsanitize=fuzzer,address", {force = true})
