Theory vfmTest0905[no_sig_docs]
Ancestors vfmTestDefs0905
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0905_0.nsv", "result0905_1.nsv", "result0905_2.nsv", "result0905_3.nsv", "result0905_4.nsv", "result0905_5.nsv", "result0905_6.nsv", "result0905_7.nsv", "result0905_8.nsv", "result0905_9.nsv", "result0905_10.nsv", "result0905_11.nsv", "result0905_12.nsv", "result0905_13.nsv", "result0905_14.nsv", "result0905_15.nsv", "result0905_16.nsv", "result0905_17.nsv", "result0905_18.nsv", "result0905_19.nsv", "result0905_20.nsv", "result0905_21.nsv", "result0905_22.nsv", "result0905_23.nsv", "result0905_24.nsv", "result0905_25.nsv", "result0905_26.nsv", "result0905_27.nsv", "result0905_28.nsv", "result0905_29.nsv", "result0905_30.nsv", "result0905_31.nsv", "result0905_32.nsv", "result0905_33.nsv", "result0905_34.nsv", "result0905_35.nsv"];
val thyn = "vfmTestDefs0905";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
