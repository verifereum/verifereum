Theory vfmTest0268[no_sig_docs]
Ancestors vfmTestDefs0268
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0268_0.nsv", "result0268_1.nsv", "result0268_2.nsv", "result0268_3.nsv", "result0268_4.nsv", "result0268_5.nsv", "result0268_6.nsv", "result0268_7.nsv", "result0268_8.nsv", "result0268_9.nsv", "result0268_10.nsv", "result0268_11.nsv", "result0268_12.nsv", "result0268_13.nsv", "result0268_14.nsv", "result0268_15.nsv", "result0268_16.nsv", "result0268_17.nsv", "result0268_18.nsv", "result0268_19.nsv", "result0268_20.nsv", "result0268_21.nsv", "result0268_22.nsv", "result0268_23.nsv", "result0268_24.nsv", "result0268_25.nsv", "result0268_26.nsv", "result0268_27.nsv", "result0268_28.nsv", "result0268_29.nsv", "result0268_30.nsv", "result0268_31.nsv", "result0268_32.nsv", "result0268_33.nsv", "result0268_34.nsv", "result0268_35.nsv", "result0268_36.nsv", "result0268_37.nsv", "result0268_38.nsv", "result0268_39.nsv"];
val thyn = "vfmTestDefs0268";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
