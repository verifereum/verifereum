Theory vfmTest1665[no_sig_docs]
Ancestors vfmTestDefs1665
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1665_0.nsv", "result1665_1.nsv", "result1665_2.nsv", "result1665_3.nsv", "result1665_4.nsv", "result1665_5.nsv", "result1665_6.nsv", "result1665_7.nsv", "result1665_8.nsv", "result1665_9.nsv", "result1665_10.nsv", "result1665_11.nsv", "result1665_12.nsv", "result1665_13.nsv", "result1665_14.nsv", "result1665_15.nsv", "result1665_16.nsv", "result1665_17.nsv", "result1665_18.nsv", "result1665_19.nsv"];
val thyn = "vfmTestDefs1665";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
