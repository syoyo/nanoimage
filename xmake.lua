add_rules("mode.debug", "mode.release")

set_languages("c11")

local core_sources = {
    "src/nanoimage_zlib.c",
    "src/nanoimage_png.c",
    "src/nanoimage_jpeg.c"
}

target("nanoimage_example")
    set_kind("binary")
    add_includedirs("include", "third_party")
    add_files("examples/load_image.c")
    add_files(core_sources)
    add_links("m")

target("nanoimage_test")
    set_kind("binary")
    add_includedirs("include", "third_party")
    add_files("tests/test_nanoimage.c")
    add_files(core_sources)
    add_links("m")

target("nanoimage_fuzz")
    set_kind("binary")
    set_toolchains("clang")
    add_includedirs("include", "third_party")
    add_files("tests/fuzz/fuzz_nanoimage.c")
    add_files(core_sources)
    add_links("m")
    add_cxflags("-fsanitize=fuzzer,address", {force = true})
    add_ldflags("-fsanitize=fuzzer,address", {force = true})
