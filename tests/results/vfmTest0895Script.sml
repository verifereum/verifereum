Theory vfmTest0895[no_sig_docs]
Ancestors vfmTestDefs0895
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0895_0.nsv", "result0895_1.nsv", "result0895_2.nsv", "result0895_3.nsv", "result0895_4.nsv", "result0895_5.nsv", "result0895_6.nsv", "result0895_7.nsv", "result0895_8.nsv", "result0895_9.nsv", "result0895_10.nsv", "result0895_11.nsv", "result0895_12.nsv", "result0895_13.nsv", "result0895_14.nsv", "result0895_15.nsv", "result0895_16.nsv", "result0895_17.nsv", "result0895_18.nsv", "result0895_19.nsv", "result0895_20.nsv", "result0895_21.nsv", "result0895_22.nsv", "result0895_23.nsv", "result0895_24.nsv", "result0895_25.nsv", "result0895_26.nsv", "result0895_27.nsv", "result0895_28.nsv", "result0895_29.nsv", "result0895_30.nsv", "result0895_31.nsv", "result0895_32.nsv"];
val thyn = "vfmTestDefs0895";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
