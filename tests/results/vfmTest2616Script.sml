Theory vfmTest2616[no_sig_docs]
Ancestors vfmTestDefs2616
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2616_0.nsv", "result2616_1.nsv", "result2616_2.nsv", "result2616_3.nsv"];
val thyn = "vfmTestDefs2616";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
