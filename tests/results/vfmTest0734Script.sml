Theory vfmTest0734[no_sig_docs]
Ancestors vfmTestDefs0734
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0734_0.nsv", "result0734_1.nsv", "result0734_2.nsv", "result0734_3.nsv", "result0734_4.nsv", "result0734_5.nsv", "result0734_6.nsv", "result0734_7.nsv", "result0734_8.nsv", "result0734_9.nsv", "result0734_10.nsv", "result0734_11.nsv", "result0734_12.nsv", "result0734_13.nsv", "result0734_14.nsv", "result0734_15.nsv", "result0734_16.nsv", "result0734_17.nsv", "result0734_18.nsv", "result0734_19.nsv", "result0734_20.nsv", "result0734_21.nsv", "result0734_22.nsv", "result0734_23.nsv", "result0734_24.nsv", "result0734_25.nsv", "result0734_26.nsv", "result0734_27.nsv", "result0734_28.nsv", "result0734_29.nsv", "result0734_30.nsv", "result0734_31.nsv", "result0734_32.nsv", "result0734_33.nsv"];
val thyn = "vfmTestDefs0734";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
