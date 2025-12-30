Theory vfmTest0179[no_sig_docs]
Ancestors vfmTestDefs0179
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0179";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
