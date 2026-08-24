Theory vfmTest0179[no_sig_docs]
Ancestors vfmTestDefs0179
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0179_0.nsv", "result0179_1.nsv", "result0179_2.nsv"];
val thyn = "vfmTestDefs0179";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
