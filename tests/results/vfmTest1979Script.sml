Theory vfmTest1979[no_sig_docs]
Ancestors vfmTestDefs1979
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1979_0.nsv", "result1979_1.nsv", "result1979_2.nsv", "result1979_3.nsv", "result1979_4.nsv", "result1979_5.nsv", "result1979_6.nsv", "result1979_7.nsv", "result1979_8.nsv", "result1979_9.nsv", "result1979_10.nsv", "result1979_11.nsv", "result1979_12.nsv", "result1979_13.nsv", "result1979_14.nsv", "result1979_15.nsv", "result1979_16.nsv", "result1979_17.nsv", "result1979_18.nsv", "result1979_19.nsv", "result1979_20.nsv", "result1979_21.nsv", "result1979_22.nsv", "result1979_23.nsv", "result1979_24.nsv", "result1979_25.nsv", "result1979_26.nsv", "result1979_27.nsv", "result1979_28.nsv", "result1979_29.nsv"];
val thyn = "vfmTestDefs1979";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
