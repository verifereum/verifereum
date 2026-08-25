Theory vfmTest2719[no_sig_docs]
Ancestors vfmTestDefs2719
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2719_0.nsv", "result2719_1.nsv", "result2719_2.nsv", "result2719_3.nsv"];
val thyn = "vfmTestDefs2719";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
