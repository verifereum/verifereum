Theory vfmTest2403[no_sig_docs]
Ancestors vfmTestDefs2403
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2403_0.nsv", "result2403_1.nsv", "result2403_2.nsv", "result2403_3.nsv", "result2403_4.nsv", "result2403_5.nsv", "result2403_6.nsv", "result2403_7.nsv", "result2403_8.nsv", "result2403_9.nsv", "result2403_10.nsv", "result2403_11.nsv", "result2403_12.nsv", "result2403_13.nsv", "result2403_14.nsv", "result2403_15.nsv", "result2403_16.nsv", "result2403_17.nsv"];
val thyn = "vfmTestDefs2403";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
