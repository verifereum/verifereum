Theory vfmTest0627[no_sig_docs]
Ancestors vfmTestDefs0627
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0627_0.nsv", "result0627_1.nsv", "result0627_2.nsv", "result0627_3.nsv", "result0627_4.nsv", "result0627_5.nsv", "result0627_6.nsv", "result0627_7.nsv", "result0627_8.nsv", "result0627_9.nsv", "result0627_10.nsv", "result0627_11.nsv", "result0627_12.nsv", "result0627_13.nsv", "result0627_14.nsv", "result0627_15.nsv", "result0627_16.nsv", "result0627_17.nsv", "result0627_18.nsv", "result0627_19.nsv", "result0627_20.nsv", "result0627_21.nsv", "result0627_22.nsv", "result0627_23.nsv", "result0627_24.nsv", "result0627_25.nsv", "result0627_26.nsv", "result0627_27.nsv", "result0627_28.nsv", "result0627_29.nsv", "result0627_30.nsv", "result0627_31.nsv", "result0627_32.nsv", "result0627_33.nsv"];
val thyn = "vfmTestDefs0627";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
