Theory vfmTest1964[no_sig_docs]
Ancestors vfmTestDefs1964
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1964_0.nsv", "result1964_1.nsv", "result1964_2.nsv", "result1964_3.nsv", "result1964_4.nsv", "result1964_5.nsv", "result1964_6.nsv", "result1964_7.nsv", "result1964_8.nsv", "result1964_9.nsv", "result1964_10.nsv", "result1964_11.nsv", "result1964_12.nsv", "result1964_13.nsv", "result1964_14.nsv", "result1964_15.nsv", "result1964_16.nsv", "result1964_17.nsv", "result1964_18.nsv", "result1964_19.nsv", "result1964_20.nsv", "result1964_21.nsv", "result1964_22.nsv", "result1964_23.nsv", "result1964_24.nsv", "result1964_25.nsv", "result1964_26.nsv", "result1964_27.nsv", "result1964_28.nsv", "result1964_29.nsv"];
val thyn = "vfmTestDefs1964";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
