Theory vfmTest1981[no_sig_docs]
Ancestors vfmTestDefs1981
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1981_0.nsv", "result1981_1.nsv", "result1981_2.nsv", "result1981_3.nsv", "result1981_4.nsv", "result1981_5.nsv", "result1981_6.nsv", "result1981_7.nsv", "result1981_8.nsv", "result1981_9.nsv", "result1981_10.nsv", "result1981_11.nsv", "result1981_12.nsv", "result1981_13.nsv", "result1981_14.nsv", "result1981_15.nsv", "result1981_16.nsv", "result1981_17.nsv", "result1981_18.nsv", "result1981_19.nsv", "result1981_20.nsv", "result1981_21.nsv", "result1981_22.nsv", "result1981_23.nsv", "result1981_24.nsv", "result1981_25.nsv", "result1981_26.nsv", "result1981_27.nsv", "result1981_28.nsv", "result1981_29.nsv"];
val thyn = "vfmTestDefs1981";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
