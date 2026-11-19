"""Regression for a proc child listing that includes sibling thread IDs."""
import tempfile
import unittest
from pathlib import Path
from replay_measure import process_tree_memory


class ProcessMemoryTest(unittest.TestCase):
    def test_threads_count_once_and_all_tasks_children_are_traversed(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            def entry(pid,group,rss,children):
                p=root/str(pid);p.mkdir(exist_ok=True)
                (p/'status').write_text(f'Pid:\t{pid}\nTgid:\t{group}\n')
                (p/'statm').write_text(f'{rss*2} {rss} 0 0 0 0 0\n')
                for task,kids in children.items():
                    q=p/'task'/str(task);q.mkdir(parents=True)
                    (q/'children').write_text(' '.join(map(str,kids)))
            # The parent lists both a thread and the child group's threads.
            entry(10,10,100,{10:[11,20,21],11:[]})
            entry(11,10,100,{})
            # A descendant is only visible from the child's second task.
            entry(20,20,200,{20:[21],21:[30,999]})
            entry(21,20,200,{})
            entry(30,30,300,{30:[]})
            # Missing999 models an already-exited process.
            self.assertEqual(process_tree_memory(10,proc=root,page_kib=4),
                             (2400,2400,3))

    def test_invalid_status_does_not_silently_disable_guard(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);p=root/'10';p.mkdir()
            (p/'status').write_text('Pid:\t10\n')
            with self.assertRaises(StopIteration):
                process_tree_memory(10,proc=root,page_kib=4)


if __name__=='__main__': unittest.main()
