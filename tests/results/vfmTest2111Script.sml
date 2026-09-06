Theory vfmTest2111[no_sig_docs]
Ancestors vfmTestDefs2111
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2111_0.nsv", "result2111_1.nsv", "result2111_2.nsv", "result2111_3.nsv", "result2111_4.nsv", "result2111_5.nsv", "result2111_6.nsv", "result2111_7.nsv", "result2111_8.nsv", "result2111_9.nsv", "result2111_10.nsv", "result2111_11.nsv", "result2111_12.nsv", "result2111_13.nsv", "result2111_14.nsv", "result2111_15.nsv", "result2111_16.nsv", "result2111_17.nsv"];
val thyn = "vfmTestDefs2111";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
