Theory vfmTest2240[no_sig_docs]
Ancestors vfmTestDefs2240
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2240_0.nsv", "result2240_1.nsv"];
val thyn = "vfmTestDefs2240";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
