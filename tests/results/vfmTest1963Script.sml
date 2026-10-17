Theory vfmTest1963[no_sig_docs]
Ancestors vfmTestDefs1963
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1963_0.nsv", "result1963_1.nsv", "result1963_2.nsv", "result1963_3.nsv", "result1963_4.nsv", "result1963_5.nsv", "result1963_6.nsv", "result1963_7.nsv", "result1963_8.nsv", "result1963_9.nsv", "result1963_10.nsv", "result1963_11.nsv", "result1963_12.nsv", "result1963_13.nsv", "result1963_14.nsv", "result1963_15.nsv", "result1963_16.nsv", "result1963_17.nsv", "result1963_18.nsv", "result1963_19.nsv"];
val thyn = "vfmTestDefs1963";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
