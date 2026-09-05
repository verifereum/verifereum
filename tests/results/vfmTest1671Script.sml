Theory vfmTest1671[no_sig_docs]
Ancestors vfmTestDefs1671
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1671_0.nsv", "result1671_1.nsv", "result1671_2.nsv", "result1671_3.nsv", "result1671_4.nsv", "result1671_5.nsv", "result1671_6.nsv", "result1671_7.nsv", "result1671_8.nsv", "result1671_9.nsv", "result1671_10.nsv", "result1671_11.nsv", "result1671_12.nsv", "result1671_13.nsv", "result1671_14.nsv", "result1671_15.nsv", "result1671_16.nsv", "result1671_17.nsv", "result1671_18.nsv", "result1671_19.nsv"];
val thyn = "vfmTestDefs1671";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
