Theory vfmTest2841[no_sig_docs]
Ancestors vfmTestDefs2841
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2841_0.nsv", "result2841_1.nsv", "result2841_2.nsv", "result2841_3.nsv"];
val thyn = "vfmTestDefs2841";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
