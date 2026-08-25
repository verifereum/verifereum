Theory vfmTest1977[no_sig_docs]
Ancestors vfmTestDefs1977
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1977_0.nsv", "result1977_1.nsv", "result1977_2.nsv", "result1977_3.nsv", "result1977_4.nsv", "result1977_5.nsv", "result1977_6.nsv", "result1977_7.nsv", "result1977_8.nsv", "result1977_9.nsv", "result1977_10.nsv", "result1977_11.nsv", "result1977_12.nsv", "result1977_13.nsv", "result1977_14.nsv", "result1977_15.nsv", "result1977_16.nsv", "result1977_17.nsv", "result1977_18.nsv", "result1977_19.nsv"];
val thyn = "vfmTestDefs1977";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
