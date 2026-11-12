Theory vfmTest0658[no_sig_docs]
Ancestors vfmTestDefs0658
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0658_0.nsv", "result0658_1.nsv", "result0658_2.nsv", "result0658_3.nsv", "result0658_4.nsv", "result0658_5.nsv", "result0658_6.nsv", "result0658_7.nsv", "result0658_8.nsv", "result0658_9.nsv", "result0658_10.nsv", "result0658_11.nsv", "result0658_12.nsv", "result0658_13.nsv", "result0658_14.nsv", "result0658_15.nsv", "result0658_16.nsv", "result0658_17.nsv", "result0658_18.nsv", "result0658_19.nsv", "result0658_20.nsv", "result0658_21.nsv"];
val thyn = "vfmTestDefs0658";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
