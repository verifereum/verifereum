Theory vfmTest2087[no_sig_docs]
Ancestors vfmTestDefs2087
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2087_0.nsv", "result2087_1.nsv", "result2087_2.nsv", "result2087_3.nsv", "result2087_4.nsv", "result2087_5.nsv", "result2087_6.nsv", "result2087_7.nsv", "result2087_8.nsv", "result2087_9.nsv", "result2087_10.nsv", "result2087_11.nsv", "result2087_12.nsv", "result2087_13.nsv", "result2087_14.nsv", "result2087_15.nsv", "result2087_16.nsv", "result2087_17.nsv"];
val thyn = "vfmTestDefs2087";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
