Theory vfmTest0388[no_sig_docs]
Ancestors vfmTestDefs0388
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0388_0.nsv", "result0388_1.nsv", "result0388_2.nsv", "result0388_3.nsv", "result0388_4.nsv", "result0388_5.nsv", "result0388_6.nsv", "result0388_7.nsv", "result0388_8.nsv", "result0388_9.nsv", "result0388_10.nsv", "result0388_11.nsv", "result0388_12.nsv", "result0388_13.nsv", "result0388_14.nsv", "result0388_15.nsv", "result0388_16.nsv", "result0388_17.nsv", "result0388_18.nsv", "result0388_19.nsv", "result0388_20.nsv", "result0388_21.nsv", "result0388_22.nsv", "result0388_23.nsv", "result0388_24.nsv", "result0388_25.nsv", "result0388_26.nsv", "result0388_27.nsv", "result0388_28.nsv", "result0388_29.nsv"];
val thyn = "vfmTestDefs0388";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
