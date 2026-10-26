Theory vfmTest1007[no_sig_docs]
Ancestors vfmTestDefs1007
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1007_0.nsv", "result1007_1.nsv", "result1007_2.nsv", "result1007_3.nsv", "result1007_4.nsv", "result1007_5.nsv", "result1007_6.nsv", "result1007_7.nsv"];
val thyn = "vfmTestDefs1007";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
