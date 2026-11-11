Theory vfmTest2155[no_sig_docs]
Ancestors vfmTestDefs2155
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2155_0.nsv", "result2155_1.nsv", "result2155_2.nsv", "result2155_3.nsv", "result2155_4.nsv", "result2155_5.nsv", "result2155_6.nsv", "result2155_7.nsv"];
val thyn = "vfmTestDefs2155";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
