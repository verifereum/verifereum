Theory vfmTest2221[no_sig_docs]
Ancestors vfmTestDefs2221
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2221_0.nsv", "result2221_1.nsv", "result2221_2.nsv", "result2221_3.nsv", "result2221_4.nsv", "result2221_5.nsv", "result2221_6.nsv", "result2221_7.nsv", "result2221_8.nsv", "result2221_9.nsv", "result2221_10.nsv", "result2221_11.nsv", "result2221_12.nsv", "result2221_13.nsv", "result2221_14.nsv", "result2221_15.nsv", "result2221_16.nsv", "result2221_17.nsv", "result2221_18.nsv", "result2221_19.nsv", "result2221_20.nsv", "result2221_21.nsv", "result2221_22.nsv", "result2221_23.nsv", "result2221_24.nsv", "result2221_25.nsv", "result2221_26.nsv", "result2221_27.nsv", "result2221_28.nsv", "result2221_29.nsv", "result2221_30.nsv", "result2221_31.nsv", "result2221_32.nsv", "result2221_33.nsv", "result2221_34.nsv", "result2221_35.nsv"];
val thyn = "vfmTestDefs2221";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
