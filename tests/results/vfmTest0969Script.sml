Theory vfmTest0969[no_sig_docs]
Ancestors vfmTestDefs0969
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0969_0.nsv", "result0969_1.nsv", "result0969_2.nsv", "result0969_3.nsv", "result0969_4.nsv", "result0969_5.nsv", "result0969_6.nsv", "result0969_7.nsv", "result0969_8.nsv", "result0969_9.nsv", "result0969_10.nsv", "result0969_11.nsv", "result0969_12.nsv", "result0969_13.nsv", "result0969_14.nsv", "result0969_15.nsv", "result0969_16.nsv", "result0969_17.nsv", "result0969_18.nsv", "result0969_19.nsv", "result0969_20.nsv", "result0969_21.nsv", "result0969_22.nsv", "result0969_23.nsv", "result0969_24.nsv", "result0969_25.nsv", "result0969_26.nsv", "result0969_27.nsv", "result0969_28.nsv", "result0969_29.nsv", "result0969_30.nsv", "result0969_31.nsv", "result0969_32.nsv", "result0969_33.nsv", "result0969_34.nsv", "result0969_35.nsv", "result0969_36.nsv", "result0969_37.nsv", "result0969_38.nsv", "result0969_39.nsv", "result0969_40.nsv", "result0969_41.nsv"];
val thyn = "vfmTestDefs0969";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
