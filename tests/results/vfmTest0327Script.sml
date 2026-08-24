Theory vfmTest0327[no_sig_docs]
Ancestors vfmTestDefs0327
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0327_0.nsv", "result0327_1.nsv", "result0327_2.nsv", "result0327_3.nsv", "result0327_4.nsv", "result0327_5.nsv", "result0327_6.nsv", "result0327_7.nsv", "result0327_8.nsv", "result0327_9.nsv", "result0327_10.nsv", "result0327_11.nsv", "result0327_12.nsv", "result0327_13.nsv", "result0327_14.nsv", "result0327_15.nsv", "result0327_16.nsv", "result0327_17.nsv", "result0327_18.nsv", "result0327_19.nsv", "result0327_20.nsv", "result0327_21.nsv", "result0327_22.nsv", "result0327_23.nsv", "result0327_24.nsv", "result0327_25.nsv", "result0327_26.nsv", "result0327_27.nsv", "result0327_28.nsv", "result0327_29.nsv", "result0327_30.nsv", "result0327_31.nsv"];
val thyn = "vfmTestDefs0327";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
