Theory vfmTest0747[no_sig_docs]
Ancestors vfmTestDefs0747
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0747_0.nsv", "result0747_1.nsv", "result0747_2.nsv", "result0747_3.nsv", "result0747_4.nsv", "result0747_5.nsv", "result0747_6.nsv", "result0747_7.nsv", "result0747_8.nsv", "result0747_9.nsv", "result0747_10.nsv", "result0747_11.nsv"];
val thyn = "vfmTestDefs0747";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
