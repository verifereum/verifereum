Theory vfmTest1975[no_sig_docs]
Ancestors vfmTestDefs1975
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1975_0.nsv", "result1975_1.nsv", "result1975_2.nsv", "result1975_3.nsv", "result1975_4.nsv", "result1975_5.nsv", "result1975_6.nsv", "result1975_7.nsv", "result1975_8.nsv", "result1975_9.nsv", "result1975_10.nsv", "result1975_11.nsv", "result1975_12.nsv", "result1975_13.nsv", "result1975_14.nsv", "result1975_15.nsv", "result1975_16.nsv", "result1975_17.nsv", "result1975_18.nsv", "result1975_19.nsv"];
val thyn = "vfmTestDefs1975";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
