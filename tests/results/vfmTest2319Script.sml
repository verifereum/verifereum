Theory vfmTest2319[no_sig_docs]
Ancestors vfmTestDefs2319
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2319_0.nsv", "result2319_1.nsv", "result2319_2.nsv", "result2319_3.nsv", "result2319_4.nsv", "result2319_5.nsv", "result2319_6.nsv", "result2319_7.nsv", "result2319_8.nsv", "result2319_9.nsv", "result2319_10.nsv", "result2319_11.nsv", "result2319_12.nsv", "result2319_13.nsv", "result2319_14.nsv", "result2319_15.nsv", "result2319_16.nsv", "result2319_17.nsv", "result2319_18.nsv", "result2319_19.nsv", "result2319_20.nsv", "result2319_21.nsv", "result2319_22.nsv", "result2319_23.nsv", "result2319_24.nsv", "result2319_25.nsv", "result2319_26.nsv", "result2319_27.nsv", "result2319_28.nsv", "result2319_29.nsv", "result2319_30.nsv", "result2319_31.nsv", "result2319_32.nsv", "result2319_33.nsv", "result2319_34.nsv", "result2319_35.nsv"];
val thyn = "vfmTestDefs2319";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
