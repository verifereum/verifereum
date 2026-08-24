Theory vfmTest1327[no_sig_docs]
Ancestors vfmTestDefs1327
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1327_0.nsv", "result1327_1.nsv", "result1327_2.nsv", "result1327_3.nsv"];
val thyn = "vfmTestDefs1327";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
