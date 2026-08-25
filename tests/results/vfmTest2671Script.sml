Theory vfmTest2671[no_sig_docs]
Ancestors vfmTestDefs2671
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2671_0.nsv", "result2671_1.nsv", "result2671_2.nsv", "result2671_3.nsv"];
val thyn = "vfmTestDefs2671";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
