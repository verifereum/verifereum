Theory vfmTest0984[no_sig_docs]
Ancestors vfmTestDefs0984
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0984_0.nsv", "result0984_1.nsv", "result0984_2.nsv", "result0984_3.nsv", "result0984_4.nsv", "result0984_5.nsv", "result0984_6.nsv", "result0984_7.nsv", "result0984_8.nsv", "result0984_9.nsv", "result0984_10.nsv", "result0984_11.nsv", "result0984_12.nsv", "result0984_13.nsv", "result0984_14.nsv", "result0984_15.nsv", "result0984_16.nsv", "result0984_17.nsv", "result0984_18.nsv", "result0984_19.nsv", "result0984_20.nsv", "result0984_21.nsv", "result0984_22.nsv", "result0984_23.nsv", "result0984_24.nsv", "result0984_25.nsv", "result0984_26.nsv", "result0984_27.nsv", "result0984_28.nsv", "result0984_29.nsv", "result0984_30.nsv", "result0984_31.nsv", "result0984_32.nsv", "result0984_33.nsv", "result0984_34.nsv", "result0984_35.nsv", "result0984_36.nsv", "result0984_37.nsv", "result0984_38.nsv", "result0984_39.nsv"];
val thyn = "vfmTestDefs0984";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
