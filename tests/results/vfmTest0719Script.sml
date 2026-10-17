Theory vfmTest0719[no_sig_docs]
Ancestors vfmTestDefs0719
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0719_0.nsv", "result0719_1.nsv", "result0719_2.nsv", "result0719_3.nsv", "result0719_4.nsv", "result0719_5.nsv", "result0719_6.nsv", "result0719_7.nsv", "result0719_8.nsv"];
val thyn = "vfmTestDefs0719";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
