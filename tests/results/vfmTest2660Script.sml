Theory vfmTest2660[no_sig_docs]
Ancestors vfmTestDefs2660
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2660_0.nsv", "result2660_1.nsv", "result2660_2.nsv", "result2660_3.nsv"];
val thyn = "vfmTestDefs2660";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
