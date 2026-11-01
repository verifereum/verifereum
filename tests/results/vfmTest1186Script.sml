Theory vfmTest1186[no_sig_docs]
Ancestors vfmTestDefs1186
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1186_0.nsv", "result1186_1.nsv", "result1186_2.nsv", "result1186_3.nsv", "result1186_4.nsv", "result1186_5.nsv", "result1186_6.nsv", "result1186_7.nsv", "result1186_8.nsv", "result1186_9.nsv", "result1186_10.nsv", "result1186_11.nsv", "result1186_12.nsv", "result1186_13.nsv", "result1186_14.nsv", "result1186_15.nsv", "result1186_16.nsv", "result1186_17.nsv", "result1186_18.nsv", "result1186_19.nsv", "result1186_20.nsv", "result1186_21.nsv", "result1186_22.nsv", "result1186_23.nsv", "result1186_24.nsv", "result1186_25.nsv", "result1186_26.nsv", "result1186_27.nsv", "result1186_28.nsv", "result1186_29.nsv", "result1186_30.nsv", "result1186_31.nsv"];
val thyn = "vfmTestDefs1186";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
