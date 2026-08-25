Theory vfmTest2812[no_sig_docs]
Ancestors vfmTestDefs2812
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2812_0.nsv", "result2812_1.nsv", "result2812_2.nsv", "result2812_3.nsv"];
val thyn = "vfmTestDefs2812";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
