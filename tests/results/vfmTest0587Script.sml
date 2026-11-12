Theory vfmTest0587[no_sig_docs]
Ancestors vfmTestDefs0587
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0587_0.nsv", "result0587_1.nsv", "result0587_2.nsv", "result0587_3.nsv", "result0587_4.nsv", "result0587_5.nsv", "result0587_6.nsv", "result0587_7.nsv", "result0587_8.nsv", "result0587_9.nsv", "result0587_10.nsv", "result0587_11.nsv", "result0587_12.nsv", "result0587_13.nsv", "result0587_14.nsv", "result0587_15.nsv", "result0587_16.nsv", "result0587_17.nsv", "result0587_18.nsv", "result0587_19.nsv", "result0587_20.nsv", "result0587_21.nsv", "result0587_22.nsv", "result0587_23.nsv"];
val thyn = "vfmTestDefs0587";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
