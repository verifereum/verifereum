Theory vfmTest0120[no_sig_docs]
Ancestors vfmTestDefs0120
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0120_0.nsv", "result0120_1.nsv", "result0120_2.nsv", "result0120_3.nsv", "result0120_4.nsv", "result0120_5.nsv"];
val thyn = "vfmTestDefs0120";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
