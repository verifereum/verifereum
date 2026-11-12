Theory vfmTest1553[no_sig_docs]
Ancestors vfmTestDefs1553
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1553_0.nsv", "result1553_1.nsv", "result1553_2.nsv", "result1553_3.nsv", "result1553_4.nsv", "result1553_5.nsv", "result1553_6.nsv", "result1553_7.nsv", "result1553_8.nsv", "result1553_9.nsv", "result1553_10.nsv", "result1553_11.nsv", "result1553_12.nsv", "result1553_13.nsv", "result1553_14.nsv", "result1553_15.nsv", "result1553_16.nsv", "result1553_17.nsv", "result1553_18.nsv", "result1553_19.nsv"];
val thyn = "vfmTestDefs1553";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
