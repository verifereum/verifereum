Theory vfmTest1674[no_sig_docs]
Ancestors vfmTestDefs1674
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1674_0.nsv", "result1674_1.nsv", "result1674_2.nsv", "result1674_3.nsv", "result1674_4.nsv", "result1674_5.nsv", "result1674_6.nsv", "result1674_7.nsv", "result1674_8.nsv", "result1674_9.nsv", "result1674_10.nsv", "result1674_11.nsv", "result1674_12.nsv", "result1674_13.nsv", "result1674_14.nsv", "result1674_15.nsv", "result1674_16.nsv", "result1674_17.nsv", "result1674_18.nsv", "result1674_19.nsv"];
val thyn = "vfmTestDefs1674";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
