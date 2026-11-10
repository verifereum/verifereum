Theory vfmTest2992[no_sig_docs]
Ancestors vfmTestDefs2992
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2992_0.nsv", "result2992_1.nsv", "result2992_2.nsv", "result2992_3.nsv", "result2992_4.nsv", "result2992_5.nsv", "result2992_6.nsv", "result2992_7.nsv", "result2992_8.nsv", "result2992_9.nsv", "result2992_10.nsv", "result2992_11.nsv", "result2992_12.nsv", "result2992_13.nsv", "result2992_14.nsv", "result2992_15.nsv", "result2992_16.nsv", "result2992_17.nsv", "result2992_18.nsv", "result2992_19.nsv", "result2992_20.nsv", "result2992_21.nsv", "result2992_22.nsv", "result2992_23.nsv", "result2992_24.nsv", "result2992_25.nsv", "result2992_26.nsv", "result2992_27.nsv", "result2992_28.nsv", "result2992_29.nsv", "result2992_30.nsv", "result2992_31.nsv", "result2992_32.nsv", "result2992_33.nsv"];
val thyn = "vfmTestDefs2992";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
