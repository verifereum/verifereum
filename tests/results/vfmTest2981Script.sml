Theory vfmTest2981[no_sig_docs]
Ancestors vfmTestDefs2981
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2981_0.nsv", "result2981_1.nsv", "result2981_2.nsv", "result2981_3.nsv", "result2981_4.nsv", "result2981_5.nsv", "result2981_6.nsv", "result2981_7.nsv", "result2981_8.nsv", "result2981_9.nsv", "result2981_10.nsv", "result2981_11.nsv", "result2981_12.nsv", "result2981_13.nsv", "result2981_14.nsv", "result2981_15.nsv", "result2981_16.nsv", "result2981_17.nsv", "result2981_18.nsv", "result2981_19.nsv", "result2981_20.nsv", "result2981_21.nsv", "result2981_22.nsv", "result2981_23.nsv", "result2981_24.nsv", "result2981_25.nsv", "result2981_26.nsv", "result2981_27.nsv", "result2981_28.nsv", "result2981_29.nsv", "result2981_30.nsv", "result2981_31.nsv"];
val thyn = "vfmTestDefs2981";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
