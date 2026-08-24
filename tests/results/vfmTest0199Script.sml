Theory vfmTest0199[no_sig_docs]
Ancestors vfmTestDefs0199
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0199_0.nsv", "result0199_1.nsv", "result0199_2.nsv", "result0199_3.nsv", "result0199_4.nsv", "result0199_5.nsv", "result0199_6.nsv", "result0199_7.nsv", "result0199_8.nsv", "result0199_9.nsv", "result0199_10.nsv", "result0199_11.nsv", "result0199_12.nsv", "result0199_13.nsv", "result0199_14.nsv", "result0199_15.nsv", "result0199_16.nsv", "result0199_17.nsv", "result0199_18.nsv", "result0199_19.nsv", "result0199_20.nsv", "result0199_21.nsv", "result0199_22.nsv", "result0199_23.nsv", "result0199_24.nsv", "result0199_25.nsv", "result0199_26.nsv", "result0199_27.nsv", "result0199_28.nsv", "result0199_29.nsv"];
val thyn = "vfmTestDefs0199";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
