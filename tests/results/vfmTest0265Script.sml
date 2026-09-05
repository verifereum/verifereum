Theory vfmTest0265[no_sig_docs]
Ancestors vfmTestDefs0265
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0265_0.nsv", "result0265_1.nsv", "result0265_2.nsv", "result0265_3.nsv", "result0265_4.nsv", "result0265_5.nsv", "result0265_6.nsv", "result0265_7.nsv", "result0265_8.nsv", "result0265_9.nsv", "result0265_10.nsv", "result0265_11.nsv", "result0265_12.nsv", "result0265_13.nsv", "result0265_14.nsv", "result0265_15.nsv", "result0265_16.nsv", "result0265_17.nsv", "result0265_18.nsv", "result0265_19.nsv", "result0265_20.nsv", "result0265_21.nsv", "result0265_22.nsv", "result0265_23.nsv", "result0265_24.nsv", "result0265_25.nsv", "result0265_26.nsv", "result0265_27.nsv", "result0265_28.nsv", "result0265_29.nsv", "result0265_30.nsv", "result0265_31.nsv"];
val thyn = "vfmTestDefs0265";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
