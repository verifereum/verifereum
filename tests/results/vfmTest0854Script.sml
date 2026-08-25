Theory vfmTest0854[no_sig_docs]
Ancestors vfmTestDefs0854
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0854_0.nsv", "result0854_1.nsv", "result0854_2.nsv", "result0854_3.nsv", "result0854_4.nsv", "result0854_5.nsv", "result0854_6.nsv", "result0854_7.nsv", "result0854_8.nsv", "result0854_9.nsv", "result0854_10.nsv", "result0854_11.nsv", "result0854_12.nsv", "result0854_13.nsv", "result0854_14.nsv", "result0854_15.nsv", "result0854_16.nsv", "result0854_17.nsv", "result0854_18.nsv", "result0854_19.nsv", "result0854_20.nsv", "result0854_21.nsv", "result0854_22.nsv", "result0854_23.nsv", "result0854_24.nsv", "result0854_25.nsv", "result0854_26.nsv", "result0854_27.nsv", "result0854_28.nsv", "result0854_29.nsv"];
val thyn = "vfmTestDefs0854";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
