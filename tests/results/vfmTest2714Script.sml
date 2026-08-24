Theory vfmTest2714[no_sig_docs]
Ancestors vfmTestDefs2714
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2714_0.nsv", "result2714_1.nsv", "result2714_2.nsv", "result2714_3.nsv", "result2714_4.nsv", "result2714_5.nsv", "result2714_6.nsv", "result2714_7.nsv", "result2714_8.nsv", "result2714_9.nsv", "result2714_10.nsv", "result2714_11.nsv", "result2714_12.nsv", "result2714_13.nsv", "result2714_14.nsv", "result2714_15.nsv", "result2714_16.nsv", "result2714_17.nsv", "result2714_18.nsv", "result2714_19.nsv", "result2714_20.nsv", "result2714_21.nsv", "result2714_22.nsv", "result2714_23.nsv", "result2714_24.nsv", "result2714_25.nsv", "result2714_26.nsv", "result2714_27.nsv", "result2714_28.nsv", "result2714_29.nsv", "result2714_30.nsv", "result2714_31.nsv", "result2714_32.nsv", "result2714_33.nsv", "result2714_34.nsv", "result2714_35.nsv", "result2714_36.nsv", "result2714_37.nsv", "result2714_38.nsv", "result2714_39.nsv"];
val thyn = "vfmTestDefs2714";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
