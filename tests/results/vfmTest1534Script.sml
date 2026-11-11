Theory vfmTest1534[no_sig_docs]
Ancestors vfmTestDefs1534
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1534_0.nsv", "result1534_1.nsv", "result1534_2.nsv", "result1534_3.nsv", "result1534_4.nsv", "result1534_5.nsv", "result1534_6.nsv", "result1534_7.nsv", "result1534_8.nsv", "result1534_9.nsv", "result1534_10.nsv", "result1534_11.nsv", "result1534_12.nsv", "result1534_13.nsv", "result1534_14.nsv", "result1534_15.nsv", "result1534_16.nsv", "result1534_17.nsv", "result1534_18.nsv", "result1534_19.nsv"];
val thyn = "vfmTestDefs1534";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
