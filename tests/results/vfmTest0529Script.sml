Theory vfmTest0529[no_sig_docs]
Ancestors vfmTestDefs0529
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0529_0.nsv", "result0529_1.nsv", "result0529_2.nsv", "result0529_3.nsv", "result0529_4.nsv", "result0529_5.nsv", "result0529_6.nsv", "result0529_7.nsv", "result0529_8.nsv", "result0529_9.nsv", "result0529_10.nsv", "result0529_11.nsv", "result0529_12.nsv", "result0529_13.nsv", "result0529_14.nsv", "result0529_15.nsv", "result0529_16.nsv", "result0529_17.nsv", "result0529_18.nsv", "result0529_19.nsv", "result0529_20.nsv", "result0529_21.nsv", "result0529_22.nsv", "result0529_23.nsv", "result0529_24.nsv", "result0529_25.nsv", "result0529_26.nsv", "result0529_27.nsv", "result0529_28.nsv", "result0529_29.nsv", "result0529_30.nsv", "result0529_31.nsv"];
val thyn = "vfmTestDefs0529";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
