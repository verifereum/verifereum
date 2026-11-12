Theory vfmTest0606[no_sig_docs]
Ancestors vfmTestDefs0606
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0606_0.nsv", "result0606_1.nsv", "result0606_2.nsv", "result0606_3.nsv", "result0606_4.nsv", "result0606_5.nsv", "result0606_6.nsv", "result0606_7.nsv", "result0606_8.nsv", "result0606_9.nsv"];
val thyn = "vfmTestDefs0606";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
