Theory vfmTest1689[no_sig_docs]
Ancestors vfmTestDefs1689
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1689_0.nsv", "result1689_1.nsv", "result1689_2.nsv", "result1689_3.nsv", "result1689_4.nsv", "result1689_5.nsv", "result1689_6.nsv", "result1689_7.nsv", "result1689_8.nsv", "result1689_9.nsv", "result1689_10.nsv", "result1689_11.nsv", "result1689_12.nsv", "result1689_13.nsv", "result1689_14.nsv", "result1689_15.nsv", "result1689_16.nsv", "result1689_17.nsv", "result1689_18.nsv", "result1689_19.nsv"];
val thyn = "vfmTestDefs1689";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
