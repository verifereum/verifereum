Theory vfmTest1561[no_sig_docs]
Ancestors vfmTestDefs1561
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1561_0.nsv", "result1561_1.nsv", "result1561_2.nsv", "result1561_3.nsv", "result1561_4.nsv", "result1561_5.nsv", "result1561_6.nsv", "result1561_7.nsv", "result1561_8.nsv", "result1561_9.nsv", "result1561_10.nsv", "result1561_11.nsv", "result1561_12.nsv", "result1561_13.nsv", "result1561_14.nsv", "result1561_15.nsv", "result1561_16.nsv", "result1561_17.nsv", "result1561_18.nsv", "result1561_19.nsv"];
val thyn = "vfmTestDefs1561";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
