Theory vfmTest2793[no_sig_docs]
Ancestors vfmTestDefs2793
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2793_0.nsv", "result2793_1.nsv", "result2793_2.nsv", "result2793_3.nsv"];
val thyn = "vfmTestDefs2793";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
