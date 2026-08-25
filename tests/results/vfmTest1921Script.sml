Theory vfmTest1921[no_sig_docs]
Ancestors vfmTestDefs1921
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1921_0.nsv", "result1921_1.nsv", "result1921_2.nsv", "result1921_3.nsv", "result1921_4.nsv", "result1921_5.nsv", "result1921_6.nsv", "result1921_7.nsv", "result1921_8.nsv", "result1921_9.nsv", "result1921_10.nsv", "result1921_11.nsv", "result1921_12.nsv", "result1921_13.nsv", "result1921_14.nsv", "result1921_15.nsv", "result1921_16.nsv", "result1921_17.nsv", "result1921_18.nsv", "result1921_19.nsv", "result1921_20.nsv", "result1921_21.nsv", "result1921_22.nsv", "result1921_23.nsv", "result1921_24.nsv", "result1921_25.nsv", "result1921_26.nsv", "result1921_27.nsv", "result1921_28.nsv", "result1921_29.nsv", "result1921_30.nsv", "result1921_31.nsv", "result1921_32.nsv", "result1921_33.nsv", "result1921_34.nsv", "result1921_35.nsv"];
val thyn = "vfmTestDefs1921";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
