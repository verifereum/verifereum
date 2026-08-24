Theory vfmTest2712[no_sig_docs]
Ancestors vfmTestDefs2712
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2712_0.nsv", "result2712_1.nsv", "result2712_2.nsv", "result2712_3.nsv"];
val thyn = "vfmTestDefs2712";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
